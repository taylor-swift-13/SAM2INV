int main1(int o,int e){
  int tz, wq, q, dzs;
  tz=40;
  wq=0;
  q=1;
  dzs=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dzs == 1 + 2*wq;
  loop invariant q == (wq + 1) * (wq + 1);
  loop invariant o >= \at(o, Pre);
  loop invariant o <= \at(o, Pre) + 2 * wq;
  loop assigns dzs, wq, q, o;
*/
while (q<=tz) {
      dzs += 2;
      wq++;
      q = q + dzs;
      o = o+(wq%3);
  }
}