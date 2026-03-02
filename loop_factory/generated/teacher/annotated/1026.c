int main1(int k,int p){
  int s, u, v, r;

  s=44;
  u=0;
  v=8;
  r=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ( (r == \at(p, Pre) && v == 8) || (r > \at(p, Pre) && v == r*r) );
  loop invariant r >= \at(p, Pre);
  loop invariant v >= 0;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant (r == \at(p, Pre) && v == 8) || v == r*r;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant r >= \at(p, Pre) && (v == 8 || v == r*r) && s == 44;
  loop invariant r >= \at(p, Pre) && v >= 0;
  loop invariant (v == r*r) || (r == \at(p, Pre) && v == 8);
  loop invariant (r > \at(p, Pre)) ==> v == r*r;
  loop invariant (v == r*r) || (r == p && v == 8);
  loop invariant r >= p;
  loop invariant s == 44;
  loop assigns r, v;
*/
while (1) {
      r = r+1;
      v = r*r;
  }

}
