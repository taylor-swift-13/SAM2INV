int main1(){
  int g3v, w, ds, qf, yq;
  g3v=1+6;
  w=g3v;
  ds=0;
  qf=w;
  yq=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g3v == 1+6;
  loop invariant w >= 0;
  loop invariant ds >= 0;
  loop invariant (qf == (g3v + ds));
  loop invariant (yq == (-6 + ds));
  loop invariant w <= g3v;
  loop assigns qf, ds, yq, w;
*/
while (w>0) {
      qf += 1;
      ds = (1)+(ds);
      yq = yq + 1;
      w = 0;
  }
}