int main1(int d,int p){
  int x, ej, qznn, o, dawt, gi;
  x=d+23;
  ej=x;
  qznn=43;
  o=0;
  dawt=1;
  gi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o + qznn == 43;
  loop invariant 0 <= qznn <= 43;
  loop invariant 1 <= dawt <= 44;
  loop invariant ej - x == dawt - 1;
  loop invariant ej <= x;
  loop assigns o, qznn, gi, ej, dawt;
*/
while (1) {
      if (!(qznn>0&&ej<x)) {
          break;
      }
      if (qznn<=dawt) {
          gi = qznn;
      }
      else {
          gi = dawt;
      }
      o += gi;
      qznn -= gi;
      ej = ej + 1;
      dawt = dawt + 1;
  }
}