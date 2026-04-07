int main1(){
  int i4h, o4, sqho;
  i4h=1+20;
  o4=0;
  sqho=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i4h == 21;
  loop invariant o4 <= i4h;
  loop invariant o4 >= 0;
  loop invariant (((sqho % 3) + 3) % 3) == (o4 % 2);
  loop invariant i4h - o4 >= 0;
  loop invariant 0 <= o4 <= i4h;
  loop invariant 0 <= i4h - o4;
  loop assigns o4, sqho;
*/
while (1) {
      if (!(o4 < i4h)) {
          break;
      }
      sqho = 1 - sqho;
      o4++;
      if ((o4%3)==0) {
          sqho = sqho + o4;
      }
  }
}