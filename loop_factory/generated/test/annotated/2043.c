int main1(){
  int b6d, a, pw, e, jd8;
  b6d=1+7;
  a=0;
  pw=b6d;
  e=-5;
  jd8=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b6d == 1 + 7;
  loop invariant e == -5;
  loop invariant 0 <= a;
  loop invariant a <= b6d;
  loop invariant jd8 % 5 == 0;
  loop invariant pw >= b6d;
  loop invariant (jd8 >= 0);
  loop assigns a, jd8, pw;
*/
while (a < b6d) {
      if (jd8 >= e) {
          jd8 = jd8 - e;
      }
      else {
          a++;
      }
      pw += b6d;
      pw = pw*pw+pw;
  }
}