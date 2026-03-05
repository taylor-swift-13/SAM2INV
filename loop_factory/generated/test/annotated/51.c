int main1(){
  int wb3, ga9, h3;
  wb3=1+6;
  ga9=wb3;
  h3=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h3 == -1;
  loop invariant wb3 == 7;
  loop invariant ga9 == wb3;
  loop assigns h3;
*/
while (ga9-2>=0) {
      h3 += 2;
      h3 -= 2;
  }
}