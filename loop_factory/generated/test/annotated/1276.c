int main1(){
  int h, b2, kt, v;
  h=1+18;
  b2=0;
  kt=4;
  v=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((h == 1 + 18 && b2 == 0 && kt == 4 && v == -6) ||
       (h == b2 && b2 == 0 && kt == 5 && v == -6));
  loop invariant b2 == 0;
  loop invariant h >= b2;
  loop invariant h <= 19;
  loop invariant kt >= 4;
  loop assigns h, kt;
*/
while (1) {
      if (!(b2+1<=h)) {
          break;
      }
      if (!(!(b2<h/2))) {
          kt++;
      }
      else {
          kt += v;
      }
      h = (b2+1)-1;
  }
}