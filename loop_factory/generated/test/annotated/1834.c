int main1(){
  int dy, s, z, igh, b;
  dy=(1%26)+8;
  s=dy;
  z=-1;
  igh=dy;
  b=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((z == -1 && igh == dy && s == dy && b == dy) ||
                  (z == igh*igh && s == 3));
  loop invariant (z == -1 || z == igh*igh);
  loop invariant (s >= 3);
  loop invariant dy == 9;
  loop invariant 0 <= igh - dy <= 1;
  loop assigns b, z, igh, s;
*/
while (s>3) {
      igh = igh + 1;
      b = b*3+(igh%5)+1;
      z = igh*igh;
      s = 3;
  }
}