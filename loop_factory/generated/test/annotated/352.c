int main1(){
  int i, cq, acti, jo, c;
  i=43;
  cq=0;
  acti=0;
  jo=0;
  c=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 0;
  loop invariant acti == jo;
  loop invariant i == 43;
  loop invariant cq >= 0;
  loop invariant c + acti == 6;
  loop invariant (cq % 2) == 0;
  loop assigns c, cq, acti, jo;
*/
while (c>0) {
      c--;
      cq = cq+1*1;
      jo = jo+1*1;
      acti = acti+1*1;
      cq = cq*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i - c == 43;
  loop invariant jo >= 0;
  loop invariant c + jo == 6;
  loop invariant i >= 43;
  loop invariant acti == 6;
  loop invariant cq >= 0;
  loop invariant c + jo == (1%18+5);
  loop invariant acti == (1%18+5);
  loop invariant 0 <= c <= 6;
  loop invariant 0 <= acti <= 6;
  loop assigns jo, c, i, cq;
*/
while (jo>=1) {
      jo -= 1;
      c = c+1*1;
      i = i+1*1;
      cq = cq+1*1;
      cq = cq + acti;
  }
}