int main1(int i,int c){
  int hm, vs, k7, s, v;
  hm=i+11;
  vs=0;
  k7=1;
  s=6;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vs == v*v*v;
  loop invariant s == 6*(v+1);
  loop invariant k7 == 3*v*v + 3*v + 1;
  loop invariant i == \at(i,Pre) + v*v*v + 6*v*v + 12*v;
  loop invariant c == \at(c,Pre) + 3*v*v + 9*v;
  loop invariant hm == \at(i,Pre) + 11;
  loop invariant v >= 0;
  loop assigns vs, v, k7, s, c, i;
*/
while (1) {
      if (!(v<=hm)) {
          break;
      }
      vs += k7;
      v++;
      k7 = k7 + s;
      s += 6;
      c = c + s;
      i = i+s+k7;
  }
}