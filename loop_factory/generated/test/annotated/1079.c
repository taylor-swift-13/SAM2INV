int main1(int w){
  int z, qf, q, x7s, t, klj, n;
  z=(w%17)+15;
  qf=z;
  q=0;
  x7s=0;
  t=0;
  klj=(w%18)+5;
  n=qf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (q == t);
  loop invariant n == z * ((((w%18) + 5) - klj) + 1);
  loop invariant t == w*w * (((w%18) + 5) - klj);
  loop invariant x7s == w*w * (((w%18) + 5) - klj);
  loop assigns t, x7s, n, klj, q;
*/
while (klj>=1) {
      t = t+w*w;
      x7s = x7s+w*w;
      n += z;
      klj--;
      q = q+w*w;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns n;
*/
for (; n>1; n = n/2) {
  }
}