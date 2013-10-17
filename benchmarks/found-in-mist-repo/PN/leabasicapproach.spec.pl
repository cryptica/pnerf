place('unlockS').
place('lockS').
place('unlockC').
place('lockC').
place('Swhile').
place('Sbefore').
place('Sbad').
place('Sin').
place('Safterin').
place('Send').
place('Cwhile').
place('Cbefore').
place('Cbad').
place('Cin').
place('Cafterin').
place('Cend').
transition(t1, ['Swhile'], ['Sbefore']).
transition(t2, ['Sbefore', 'unlockS'], ['Sbad', 'lockS']).
transition(t3, ['Sbad', 'unlockC'], ['Sin', 'lockC']).
transition(t4, ['Sin', 'lockC'], ['Safterin', 'unlockC']).
transition(t5, ['Safterin', 'lockS'], ['Send', 'unlockS']).
transition(t6, ['Send'], ['Swhile']).
transition(t7, ['Cwhile'], ['Cbefore']).
transition(t8, ['Cbefore', 'unlockC'], ['Cbad', 'lockC']).
transition(t9, ['Cbad', 'unlockS'], ['Cin', 'lockS']).
transition(t10, ['Cin', 'lockS'], ['Cafterin', 'unlockS']).
transition(t11, ['Cafterin', 'lockC'], ['Cend', 'unlockC']).
transition(t12, ['Cend'], ['Cwhile']).
init('unlockS', 1).
init('unlockC', 1).
init('Swhile', init1).
cond('(>= init1 1)').
init('Cwhile', init2).
cond('(>= init2 1)').
cond('(>= Sbad 1)').
target('Sbad', 1).
cond('(>= Cbad 1)').
target('Cbad', 1).
