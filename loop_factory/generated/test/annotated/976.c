int main1(){
  int s2aa, t, doa, i0;
  s2aa=1*3;
  t=3;
  doa=-1;
  i0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 3;
  loop invariant ((doa + 1) % 4 == 0);
  loop invariant i0 == ((doa + 1) * (doa + 3)) / 8;
  loop invariant (doa >= -1);
  loop invariant s2aa == t;
  loop assigns doa, i0, s2aa;
*/
while (t+1<=s2aa) {
      doa += 4;
      i0 += doa;
      s2aa = ((t+1))+(-(1));
  }
}