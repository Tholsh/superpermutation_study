# Corpus layout through N=9

Every file under `words/5` through `words/9` is a plain `.txt` containing one complete superpermutation, with one-based labels `123…N`. Each word was checked for all `N!` permutations after normalization. Lengths are unchanged. N=10 and above were left unchanged.

Individual source files keep their names. A former collection such as `words/6/872-treelike.txt.gz` becomes a folder, `words/6/872-treelike/`, containing `872-00001.txt`, `872-00002.txt`, and so on. The number is the word's ordinal in the original collection. ZIP collections have an archive folder followed by a member-collection folder. Repeated source occurrences are retained separately.

[`normalization-n1-n9.json`](normalization-n1-n9.json) records each changed source or ZIP member, its original content hash, output folder or filename, and original word-line numbers. Collection hashes cover the normalized words in source order, each followed by a newline. An existing individual file that already satisfied the layout is unchanged and needs no migration entry.

Author README files, cycle descriptions, and comments from mixed word/comment files live here under their corresponding `N` and source directories. `.notes.txt` contains the original nonblank comment lines in order. Other supporting files retain their original bytes; the compressed N=6 two-cycle descriptions remain compressed. Line 1 of `6/872-treelike-2cycles.txt.gz` corresponds to `words/6/872-treelike/872-00001.txt`, and so on. ZIP member metadata is retained; macOS resource forks and `.DS_Store` files are excluded.

For example, from the repository root in PowerShell:

```powershell
Get-Content words/6/872-treelike/872-00001.txt | ./paint-waste.exe -s 6
Get-Content words/9/superpermutation-9-408731.txt | ./paint-waste.exe -s 9
```

Both use the default one-based alphabet. Each should report `missing_permutations: 0` and `valid_superpermutation: 1`.
