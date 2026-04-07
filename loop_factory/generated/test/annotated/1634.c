int main1(){
  int q3, s77, vit;
  q3=1;
  s77=0;
  vit=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vit == 0;
  loop invariant s77 % 10 == 0;
  loop invariant s77 >= 0;
  loop invariant (q3 == 1);
  loop assigns s77, vit;
*/
while (s77<=q3-1) {
      vit = q3-s77;
      s77 = s77 + 10;
      vit = (vit)+(-(vit));
  }
}