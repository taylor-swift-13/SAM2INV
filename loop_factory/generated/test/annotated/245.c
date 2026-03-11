int main1(int m,int j){
  int ek, vj, yae, mb0, rc;
  ek=21;
  vj=3;
  yae=0;
  mb0=j;
  rc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yae == rc;
  loop invariant yae <= ek;
  loop invariant (yae > 0) ==> (mb0 == yae - 1);
  loop invariant 0 <= yae;
  loop assigns mb0, rc, yae;
*/
while (yae<ek) {
      if (rc<ek) {
          mb0 = yae;
      }
      rc = rc + 1;
      yae++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mb0 >= 0;
  loop invariant ek >= 0;
  loop invariant vj == 3 + ek * ((mb0 - (ek - 1)) * (mb0 + (ek - 1) - 1) / 2);
  loop invariant 3 <= vj;
  loop assigns vj, j, mb0;
*/
while (mb0-1>=0) {
      vj = vj+ek*mb0;
      j += vj;
      mb0 = mb0 + 1;
  }
}