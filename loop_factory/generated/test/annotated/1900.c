int main1(int l,int w){
  int q1, va, n, a8, by, s, as, jf, vpp;
  q1=w+11;
  va=0;
  n=q1;
  a8=0;
  by=va;
  s=q1;
  as=w;
  jf=0;
  vpp=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q1 == \at(w, Pre) + 11;
  loop invariant 0 <= va;
  loop invariant a8 >= 0;
  loop invariant as >= \at(w, Pre);
  loop invariant jf >= 0;
  loop invariant w >= \at(w, Pre);
  loop invariant l == \at(l, Pre);
  loop invariant n >= q1;
  loop invariant n - w - 11 == 4 * va;
  loop invariant vpp == \at(w, Pre);
  loop invariant s >= q1;
  loop assigns w, n, a8, by, s, as, jf, va;
*/
while (va < q1) {
      if ((((l + va) % 3) == 0)) {
          s++;
      }
      if ((((l + va) % 3) == 1)) {
          as += 1;
      }
      if ((((l + va) % 3) == 2)) {
          jf++;
      }
      by = (by+as)%3;
      w = w + s;
      n = n + s;
      va += 1;
      a8 = a8 + s;
      a8 += 2;
      n += 1;
      if (vpp+5<q1) {
          a8 = a8 + va;
      }
      n = n + 3;
  }
}