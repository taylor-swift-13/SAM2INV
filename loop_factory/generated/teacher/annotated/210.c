int main1(int k,int m){
  int o, x, v, w;

  o=m-9;
  x=0;
  v=k;
  w=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(k, Pre) || v <= o + x;
  loop invariant x == 0;
  loop invariant o == \at(m, Pre) - 9;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (x == 0 && v == \at(k, Pre)) || v <= o + x;
  loop invariant x >= 0;
  loop invariant o < 0 || x <= o;
  loop invariant o == m - 9;
  loop invariant x == 0 && ((v <= o) || (v <= k));
  loop invariant ((v <= k) || (v <= o));
  loop assigns v;
*/
while (x<=o-1) {
      if (v+5<=o) {
          v = v+5;
      }
      else {
          v = o;
      }
      v = v+x;
  }

}
