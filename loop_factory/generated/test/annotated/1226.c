int main1(int r,int z){
  int w, l5, s, l3v, wz;
  w=(r%18)+9;
  l5=-6;
  s=w;
  l3v=-1;
  wz=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == (\at(r,Pre) % 18) + 9;
  loop invariant l3v == -1 + 6*(wz - 3);
  loop invariant s == w + 3*(wz - 3)*(wz - 3) - 4*(wz - 3);
  loop invariant l5 == -6 + (wz - 3)*w + ((wz - 4)*(wz - 3)*(2*wz - 11))/2;
  loop invariant z == \at(z,Pre) + (wz - 3)*w + ((wz - 3)*(wz - 2)*(2*wz - 9))/2;
  loop invariant s == ((\at(r,Pre) % 18) + 9) + 3*(wz - 3)*(wz - 3) - 4*(wz - 3);
  loop invariant l5 == z + (-6 - \at(z,Pre)) - (3*(wz - 3)*(wz - 3) - 4*(wz - 3));
  loop assigns l5, s, z, r, wz, l3v;
*/
while (wz<=w) {
      l5 = l5 + s;
      s = s + l3v;
      z = z + s;
      r = r*2;
      wz++;
      l3v += 6;
  }
}