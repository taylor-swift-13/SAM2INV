int main1(int k,int p){
  int u, a, o, v;

  u=(k%17)+14;
  a=1;
  o=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == (\at(k,Pre) % 17) + 14;

  loop invariant o >= 0;
  loop invariant (o <= u/2) ==> (v == -5);

  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == (k % 17) + 14;
  loop invariant v >= -5;

  loop invariant (k == \at(k, Pre)) && (p == \at(p, Pre));

  loop invariant (o <= u/2) ==> v == -5;

  loop invariant (o < u/2) ==> (v == -5);

  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant 0 <= o;
  loop invariant o < u/2 ==> v == -5;


  loop invariant u == \at(k, Pre) % 17 + 14;

  loop invariant -5 <= v && v <= -5 + 2*o;
  loop assigns v, o;
*/
while (o<u) {
      if (o>=u/2) {
          v = v+2;
      }
      o = o+1;
  }
/*@
  assert !(o<u) &&
         (u == (\at(k,Pre) % 17) + 14);
*/


}
