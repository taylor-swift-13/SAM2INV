int main1(){
  int p, b, edz, dbp, mwwd, o;
  p=1*5;
  b=0;
  edz=(1%40)+2;
  dbp=0;
  mwwd=p;
  o=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 0;
  loop invariant p == 5;
  loop invariant mwwd == p;
  loop invariant edz > 0;
  loop invariant edz <= p;
  loop invariant 0 <= dbp <= p;
  loop assigns dbp, mwwd, edz;
*/
while (edz!=dbp) {
      dbp = edz;
      mwwd += b;
      edz = (edz+p/edz)/2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 5;
  loop invariant o == p;
  loop invariant edz > 0;
  loop invariant dbp >= 0;
  loop invariant mwwd >= 0;
  loop invariant mwwd <= p;
  loop invariant edz <= p;
  loop assigns dbp, edz, mwwd;
*/
while (edz!=mwwd) {
      mwwd = edz;
      edz = (edz+o/edz)/2;
      dbp = dbp + edz;
  }
}