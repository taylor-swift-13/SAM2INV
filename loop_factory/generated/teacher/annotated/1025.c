int main1(int b,int k){
  int v, z, o, f;

  v=(k%9)+4;
  z=0;
  o=z;
  f=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(k, Pre) % 9 + 4;
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant f >= 2;
  loop invariant o >= 0;
  loop invariant o - 2*f + 4 >= 0;
  loop invariant k == \at(k, Pre) && b == \at(b, Pre);
  loop invariant b == \at(b, Pre) && f >= 2 && o >= 0;
  loop invariant v == (\at(k, Pre) % 9 + 4) && f >= 2;
  loop invariant k == \at(k, Pre) && b == \at(b, Pre) && o >= 0;
  loop invariant v == \at(k,Pre) % 9 + 4;
  loop invariant k == \at(k,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant f >= 2 && o >= 0;
  loop assigns o, f;
*/
while (1) {
      o = o+3;
      f = f+o;
      o = o+f+f;
  }

}
