int main1(int y,int v){
  int mek, p, c, ngg, crb;
  mek=v;
  p=mek;
  c=(v%40)+2;
  ngg=0;
  crb=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant crb + c == v + (v % 40) + 2;
  loop invariant crb == \at(v,Pre) + ((\at(v,Pre) % 40) + 2) - c;
  loop invariant mek == v;
  loop assigns ngg, c, crb;
*/
while (c!=ngg) {
      ngg = c;
      c = (c+mek/c)/2;
      crb = (crb+ngg)+(-(c));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mek == v;
  loop assigns p, c, crb;
*/
while (c!=crb) {
      crb = c;
      c = (c+mek/c)/2;
      p = p + mek;
  }
}