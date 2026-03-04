int main1(int l,int z){
  int scq, w8, s;
  scq=l+14;
  w8=0;
  s=scq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant scq == \at(l, Pre) + 14;
  loop invariant s == scq + 3*w8;
  loop invariant l == \at(l, Pre) + 3*w8;
  loop invariant z == \at(z, Pre) + w8*scq + (3*w8*(w8+1))/2;
  loop invariant l - 3*w8 == \at(l, Pre);
  loop invariant s - 3*w8 == scq;
  loop invariant z - w8*scq - 3*w8*(w8+1)/2 == \at(z, Pre);
  loop assigns s, w8, l, z;
*/
while (1) {
      if (!(w8<scq)) {
          break;
      }
      s = s + 3;
      w8++;
      l = l + 3;
      z = z + s;
  }
}