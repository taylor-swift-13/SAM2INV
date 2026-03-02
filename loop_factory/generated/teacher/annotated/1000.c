int main1(int b,int m){
  int o, k, v, w;

  o=74;
  k=0;
  v=k;
  w=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k <= o;
  loop invariant v >= 0;
  loop invariant v % 3 == 0;
  loop invariant w >= -6;
  loop invariant w % 3 == 0;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant w + 2*v + 6 >= 0;
  loop invariant o == 74;
  loop invariant k == 0;
  loop invariant v >= 0 && v % 3 == 0;
  loop invariant (w + 2*v + 12) % 6 == 0 && w + 2*v + 12 >= 6;
  loop invariant w % 2 == 0;

  loop invariant 0 <= k && k <= o;
  loop invariant v % 3 == 0 && v >= 0;
  loop invariant (w + 2*v + 12) % 6 == 0 && (w + 2*v + 12) >= 6;
  loop invariant k == 0 && k <= o && v >= 0 && w + 2*v + 12 > 0;
  loop invariant v % 3 == 0 && w % 2 == 0 && o == 74 && 0 <= k && k <= o;
  loop assigns v, w;
*/
while (k<=o-1) {
      v = v+3;
      w = w+v;
      w = w+w;
  }

}
