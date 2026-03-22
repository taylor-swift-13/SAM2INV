int main1(){
  int q6, bu1, ans, ev;
  q6=1;
  bu1=0;
  ans=6;
  ev=bu1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (bu1 + 1) <= q6 <= (bu1 + 2);
  loop invariant (ans == 6) || (ans == 7);
  loop invariant bu1 == 0;
  loop invariant ev == bu1;
  loop assigns ans, q6;
*/
while (bu1+3<=q6) {
      if (!(!(bu1<q6/2))) {
          ans++;
      }
      else {
          ans = ans + ev;
      }
      q6 = (bu1+3)-1;
  }
}