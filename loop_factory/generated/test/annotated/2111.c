int main1(){
  int t, q5o5, miqp;
  t=1+7;
  q5o5=0;
  miqp=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q5o5 == 0;
  loop invariant (t == q5o5 + 2) || (t >= q5o5 + 3);
  loop invariant miqp >= 1;
  loop assigns miqp, t;
*/
while (q5o5+3<=t) {
      if (miqp+1<=t) {
          miqp++;
      }
      else {
          miqp = t;
      }
      t = (q5o5+3)-1;
  }
}