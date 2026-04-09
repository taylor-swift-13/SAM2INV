int main1(int z){
  int q, kj, c, s;
  q=18;
  kj=0;
  c=0;
  s=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= kj;
  loop invariant kj <= q;
  loop invariant s == z;
  loop invariant (kj <= q/2 ==> c == 3*kj) && (kj >= q/2 ==> c == kj + q);
  loop invariant (2*kj <= q ==> c == 3*kj) && (2*kj >= q ==> c == kj + q);
  loop invariant ((kj <= 9) && c == 3*kj) || ((kj >= 9) && c == kj + 18);
  loop invariant ((kj <= 9) && s == \at(z, Pre) + 3*kj*(kj+1)/2) ||
                   ((kj >= 9) && s == \at(z, Pre) + (kj*(kj+1)/2 + 18*kj - 72));
  loop invariant (2*kj >= q) ==> (c == kj + 2*(q/2));
  loop assigns kj, c, s, z;
*/
while (kj < q) {
      kj = (c += (2*kj < q ? 1 : -1), kj + 1);
      c += 2;
      s = s + c;
      z = z + c;
  }
}