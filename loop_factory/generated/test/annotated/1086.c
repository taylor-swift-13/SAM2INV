int main1(int d,int t){
  int ad, aw0, ro, t5;
  ad=t;
  aw0=0;
  ro=(d%28)+10;
  t5=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ro == ((\at(d,Pre) % 28) + 10) - ((aw0 * (aw0 - 1)) / 2);
  loop invariant d == \at(d,Pre) + ((aw0 * (aw0 + 1)) / 2);
  loop invariant t == \at(t,Pre);
  loop invariant aw0 >= 0;
  loop invariant ad == \at(t,Pre);
  loop assigns ro, aw0, t5, d;
*/
while (ro>aw0) {
      ro -= aw0;
      aw0 = aw0 + 1;
      t5++;
      t5 = t5*2+5;
      d += aw0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= \at(t,Pre);
  loop invariant ad >= \at(t,Pre);
  loop assigns t5, ad, t, d;
*/
while (t5>ad) {
      t5 = t5 - ad;
      ad += 1;
      t = t+(t5%5);
      d = (ro)+(d);
  }
}