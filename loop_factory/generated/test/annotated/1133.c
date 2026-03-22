int main1(int v,int s){
  int j7, vq, u1, x5, tas, ln, wp1;
  j7=v+16;
  vq=3;
  u1=6;
  x5=6;
  tas=0;
  ln=7;
  wp1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u1;
  loop invariant u1 <= ln;
  loop invariant j7 == \at(v, Pre) + 16;
  loop invariant x5 >= 6;
  loop invariant v == \at(v, Pre);
  loop invariant s == \at(s, Pre);
  loop invariant vq == wp1 + 3;
  loop invariant 0 <= tas;
  loop invariant tas <= wp1;
  loop assigns wp1, vq, u1, x5, tas;
*/
while (vq<j7) {
      if (!(!(vq%3==0))) {
          if (u1>0) {
              u1 -= 1;
              tas++;
          }
      }
      else {
          if (u1<ln) {
              u1++;
              x5 += 1;
          }
      }
      wp1++;
      vq = vq + 1;
  }
}