int main1(int p){
  int e9hs, t8s, ezt, xs1, pb;
  e9hs=p*5;
  t8s=0;
  ezt=t8s;
  xs1=-3;
  pb=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ezt == 0;
  loop invariant t8s >= 0;
  loop invariant e9hs == 5 * p;
  loop invariant (e9hs >= 0) ==> (t8s <= e9hs);
  loop invariant (t8s == 0) ==> (xs1 == -3);
  loop invariant p == \at(p, Pre);
  loop assigns ezt, t8s, pb, xs1;
*/
while (t8s < e9hs) {
      ezt = ezt * p;
      t8s += 1;
      pb = pb * p;
      xs1 = xs1 * p;
  }
}