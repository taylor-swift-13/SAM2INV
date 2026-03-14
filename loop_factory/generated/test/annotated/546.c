int main1(int z,int q){
  int go, zu, n9f, ue, vp, m3q;
  go=(z%26)+4;
  zu=5;
  n9f=0;
  ue=0;
  vp=8;
  m3q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m3q == zu * n9f;
  loop invariant 0 <= n9f;
  loop invariant vp == 8 - n9f;
  loop invariant n9f <= 8;
  loop invariant ue == n9f * (17 - n9f) / 2;
  loop invariant go == (z % 26) + 4;
  loop assigns ue, n9f, m3q, vp;
*/
while (n9f<go&&vp>0) {
      ue += vp;
      n9f += 1;
      m3q = m3q + zu;
      vp = vp - 1;
  }
}