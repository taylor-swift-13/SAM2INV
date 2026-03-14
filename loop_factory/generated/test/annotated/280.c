int main1(){
  int rn4, nv5h, wy, po6k, jw, z6;
  rn4=1*2;
  nv5h=0;
  wy=23;
  po6k=0;
  jw=1;
  z6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jw == nv5h + 1;
  loop invariant po6k + wy == 23;
  loop invariant wy >= 0;
  loop invariant po6k >= 0;
  loop invariant 0 <= nv5h;
  loop invariant nv5h <= rn4;
  loop assigns z6, po6k, nv5h, wy, jw;
*/
while (wy>0&&nv5h<rn4) {
      if (wy<=jw) {
          z6 = wy;
      }
      else {
          z6 = jw;
      }
      po6k += z6;
      nv5h++;
      wy -= z6;
      jw = jw + 1;
  }
}