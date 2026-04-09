int main1(int i){
  int e, cx, vfkn, sy, oz;
  e=i+17;
  cx=0;
  vfkn=2;
  sy=vfkn;
  oz=vfkn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (sy == vfkn);
  loop invariant e == \at(i, Pre) + 17;
  loop invariant cx >= 0;
  loop invariant oz == sy;
  loop invariant (e >= 0 ==> cx <= e);
  loop assigns oz, sy, cx;
*/
while (cx < e) {
      oz = sy;
      sy = vfkn;
      cx = cx + 1;
  }
}