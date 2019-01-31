import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here 
        if isinstance(fact_or_rule, Fact): # if the input is a fact 
            if fact_or_rule in self.facts: # if the input fact is in our kb
                fact = self._get_fact(fact_or_rule) #find this fact from our kb 
                self.kb_retract_recursive(fact) 

    def kb_retract_recursive(self, fact_or_rule):
        #If the input is a fact
        if isinstance(fact_or_rule, Fact):
            if not fact_or_rule.supported_by: # if this input is not supported by anything  
                #For FACTS  "fact_or_rule" supports: 
                for x in fact_or_rule.supports_facts: # find all the facts it supports:
                    for fact, rule in x.supported_by: # go through each of these facts' supported_by" list, delete everything associated with fact_or_rule
                        if fact_or_rule==fact: 
                            x.supported_by.remove([fact, rule])

                    #after deleting input from the supported by list,  
                    #remove if x's "supported_by" list is empty, and if it is not an asserted fact     
                    if not x.supported_by and not x.asserted: 
                        # we should remove it but we need to check whether it supports other things, 
                        #so we need to go through the loop again. Evantually it will remove everything 
                        self.kb_retract_recursive(x)
                
                #For RULES "fact_or_rule" supports: (same thing)
                for y in fact_or_rule.supports_rules: 
                    for fact, rule in y.supported_by:
                        if fact_or_rule==fact:
                            y.supported_by.remove([fact, rule])
                    if not y.supported_by and not y.asserted:
                        self.kb_retract_recursive(y)
                
                self.facts.remove(fact_or_rule)
            #else if the input is supported by other fact and is asserted   
            elif fact_or_rule.asserted:
                fact_or_rule.asserted = False

            #else if the input is supported but not asserted (i.e. referred), you do nothing
        
             
        #If the input is a rule
        elif isinstance(fact_or_rule, Rule):
            if not fact_or_rule.supported_by:
                for x in fact_or_rule.supports_facts:
                    for fact, rule in x.supported_by:
                        if fact_or_rule==rule:
                            x.supported_by.remove([fact, rule])
                    if not x.supported_by and not x.asserted:
                        self.kb_retract_recursive(x)

                for y in fact_or_rule.supports_rules:
                    for fact, rule in y.supported_by:
                        if fact_or_rule==rule:
                            y.supported_by.remove([fact, rule])
                    if not y.supported_by and not y.asserted:
                        self.kb_retract_recursive(y)
                self.rules.remove(fact_or_rule)
            
            elif fact_or_rule.asserted:
                fact_or_rule.asserted = False


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        binding_inf=match(fact.statement, rule.lhs[0]) 
        if binding_inf:  
            if len(rule.lhs)>1: # if ther are more than 1 lhs, create new rule
                new_lhs=[]
                for i in range(1,len(rule.lhs)): 
                    new_lhs.append(instantiate(rule.lhs[i], binding_inf)) #instantiate lhs and add to new lhs list
                    new_rhs=instantiate(rule.rhs, binding_inf) #instatntiate rhs 
                    new_rule=Rule([new_lhs, new_rhs], [[fact,rule]])
                    kb.kb_add(new_rule) 
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)

            
            else: # if there is only 1 lhs, create new fact
                fact_sta = instantiate(rule.rhs, binding_inf) #instatntiate rhs
                new_fact=Fact(fact_sta, [[fact,rule]])
                kb.kb_add(new_fact)
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
       # add f and r to supports_list 
        

 


