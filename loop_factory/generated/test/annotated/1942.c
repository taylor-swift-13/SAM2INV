int main1(int w){
  int v, tj, kzo, ztj;
  v=20;
  tj=0;
  kzo=0;
  ztj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tj;
  loop invariant tj <= v;
  loop invariant kzo == ztj;
  loop invariant (tj == 0 && ztj == 0) || (tj >= 1 && ztj == \at(w, Pre));
  loop invariant ( (\at(w, Pre) >= 0) ==> (0 <= ztj && ztj <= \at(w, Pre)) )
                   && ( (\at(w, Pre) < 0)  ==> (\at(w, Pre) <= ztj && ztj <= 0) );
  loop invariant v == 20;
  loop assigns ztj, kzo, tj;
*/
while (1) {
      if (!(tj < v)) {
          break;
      }
      ztj = ztj + (w - ztj) / (tj + 1);
      kzo = ztj;
      tj = tj + 1;
  }
}