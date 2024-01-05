sig Pengguna {
    posts: set Post
}

sig Post {}

sig JaringanSosialMedia {
    posts: Pengguna -> Post, 
    teman: Pengguna -> Pengguna,
    servers: set Server
}

sig Server {
    posts: Pengguna -> Post,
    kapasitas: Int
}

some sig inisialisasiJaringanSosialMedia in JaringanSosialMedia {}{
    #posts=0
    #teman=0
    #servers=0
    all s : servers | #s.posts = 0 and s.kapasitas > 0
}

pred operasiPost[n1, n2 : JaringanSosialMedia] {
    n2.teman = n1.teman
    n2.servers = n1.servers
}

pred invariant[n : JaringanSosialMedia] {
    all p : Post | lone n.posts.p
    no u : Pengguna | u -> u in n.teman
    n.teman = ~(n.teman)
    all s : n.servers | #s.posts <= s.kapasitas
    all s1, s2 : n.servers | s1 != s2 implies no (s1.posts[Pengguna] & s2.posts[Pengguna])
}

pred tambahPost[n1, n2 : JaringanSosialMedia, u : Pengguna, p : Post] {
    p not in n1.posts[Pengguna]
    n2.posts = n1.posts + u -> p
    operasiPost[n1, n2]
}

pred hapusPost[n1, n2 : JaringanSosialMedia, u : Pengguna, p : Post] {
    u -> p in n1.posts
    n2.posts = n1.posts - u -> p
    operasiPost[n1, n2]
}

pred tambahTeman[n1, n2 : JaringanSosialMedia, u, v : Pengguna] {
    v not in n1.teman[Pengguna]
    n2.teman = n1.teman + u -> v
    operasiPost[n1, n2]
}

pred hapusTeman[n1, n2 : JaringanSosialMedia, u, v : Pengguna] {
    v in n1.teman[u]
    n2.teman = n1.teman - u -> v
    operasiPost[n1, n2]
}

pred tambahServer[n1, n2 : JaringanSosialMedia, s : Server] {
    s not in n1.servers
    n2.servers = n1.servers + s
    operasiPost[n1, n2]
}

pred hapusServer[n1, n2 : JaringanSosialMedia, s : Server] {
    s in n1.servers
    n2.servers = n1.servers - s
    operasiPost[n1, n2]
}

// CHECKING WHETHER THE ABOVE INVARIANTS ARE PRESERVED
// 1. Pengecekan penambahan post
assert tambahPostPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, u : Pengguna, p : Post |
        invariant[n1] and tambahPost[n1, n2, u, p] implies
            invariant[n2]
}
//check tambahPostPertahankanInv for 4 but exactly 1 JaringanSosialMedia

//2. Pengecekan penghapusan post
assert hapusPostPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, u : Pengguna, p : Post |
        invariant[n1] and hapusPost[n1, n2, u, p] implies
            invariant[n2]
}
//check hapusPostPertahankanInv for 4 but exactly 1 JaringanSosialMedia

//3. Pengecekan penambahan teman
assert tambahTemanPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, u, v : Pengguna |
        invariant[n1] and tambahTeman[n1, n2, u, v] implies
            invariant[n2]
}
//check tambahTemanPertahankanInv for 4 but exactly 1 JaringanSosialMedia

//4. Pengecekan penghapusan teman
assert hapusTemanPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, u, v : Pengguna |
        invariant[n1] and hapusTeman[n1, n2, u, v] implies
            invariant[n2]
}
//check hapusTemanPertahankanInv for 4 but exactly 1 JaringanSosialMedia

//5. Pengecekan penambahan server
assert tambahServerPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, s : Server |
        invariant[n1] and tambahServer[n1, n2, s] implies
            invariant[n2]
}
//check tambahServerPertahankanInv for 4 but exactly 1 JaringanSosialMedia

//6. Pengecekan penghapusan server
assert hapusServerPertahankanInv {
    // base case
    all jsm : inisialisasiJaringanSosialMedia | invariant[jsm]
    // inductive case
    all n1, n2 : JaringanSosialMedia, s : Server |
        invariant[n1] and hapusServer[n1, n2, s] implies
            invariant[n2]
}
//check hapusServerPertahankanInv for 4 but exactly 1 JaringanSosialMedia

// CHECKING ALGEBRAIC PROPERTIES
// memeriksa apakah jika kita menambahkan postingan lalu menghapusnya, apakah masih original state?
/*
check HapusPostMembatalkanTambahPost {
    all n1, n2, n3 : JaringanSosialMedia, u : Pengguna, p : Post |
        invariant[n1] and tambahPost[n1, n2, u, p] and hapusPost[n2, n3, u, p] implies
            n1.posts = n3.posts
}
*/



run {} for 5 but exactly 1 JaringanSosialMedia

