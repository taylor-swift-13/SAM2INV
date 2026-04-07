int main1(){
  int a, v2i, mm, c, guq2;
  a=1;
  v2i=0;
  mm=-5;
  c=a;
  guq2=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 0;
  loop invariant mm <= -5;
  loop invariant a >= v2i;
  loop invariant a <= v2i + 1;
  loop invariant guq2 == 1 + (4*(mm + 5))/3;
  loop assigns a, c, guq2, mm;
*/
while (v2i+1<=a) {
      c = c/4;
      mm = mm*4;
      guq2 += mm;
      a = (v2i+1)-1;
  }
}