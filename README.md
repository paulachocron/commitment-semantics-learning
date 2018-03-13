README

For experiment 1, the program will print the propotion of interactions in which the student did not violate a commitment

For experiment 2, the program prints the original specification, the learned one, and the precision and recall obtained by the student after observing all the interactions, for each iteration. When all the iterations end, it prints the average precision.

Notes:

    The type argument indicates which of the variations of the second experiment will be performed:

    create: only creates in spec
    release: only create + release in spec
    basic: cancels in spec
    frequency: frequency extension. Use -r argument to set discharges/cancels ratio
    punish: punishment extension
    -policy: policy

    The experiments can be quite slow with large vocabularies due to the amount of possibilities. We suggest to keep it <10. For larger vocabularies, increase the number of interactions observed.

    The experiment 1 uses the same number (-r) for the number of experiments and for the repetitions in each experiment

    Verbose = 1 should only be used for debugging or analysis, since it prints a lot of information. Verbose = 0 prints minimal informative data

    The write option for experiment 2 saves the precision and recall data that is shown in the paper in a file with name 'results'+voc+'-'+type+'-'+frequency
