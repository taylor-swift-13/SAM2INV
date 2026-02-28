int main1(int k,int p){
  int h, o, v, s, w, x;

  h=(k%12)+16;
  o=0;
  v=h;
  s=k;
  w=k;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o <= h;
  loop invariant o >= 0;
  loop invariant w == k + o*v;
  loop invariant s == k*(1+o) + v*o*(o-1)/2;
  loop invariant h == (\at(k,Pre) % 12) + 16;
  loop invariant v == h;
  loop invariant s == k*(o+1) + v*o*(o-1)/2;
  loop invariant w == k + v*o;
  loop invariant 2*s == 2*k*(o+1) + v*o*(o-1);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == (\at(k, Pre) % 12) + 16;
  loop invariant 0 <= o;
  loop invariant w == \at(k, Pre) + o * v;

  loop assigns s, w, o;
*/
while (o<h) {
      s = s+w;
      w = w+v;
      o = o+1;
  }

}
