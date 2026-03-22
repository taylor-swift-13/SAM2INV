int main1(){
  int ay, l0, q, s, yhk2;
  ay=1;
  l0=(1%20)+1;
  q=(1%25)+1;
  s=0;
  yhk2=ay;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ay == 1;
  loop invariant q >= 0;
  loop invariant s >= 0;
  loop invariant q <= 2;
  loop invariant l0 % 2 == 0;
  loop invariant yhk2 >= 1;
  loop invariant l0 >= 2;
  loop assigns s, q, l0, yhk2;
*/
while (q!=0) {
      if (q%2==1) {
          s += l0;
          q = q - 1;
      }
      else {
      }
      q = q/2;
      l0 = 2*l0;
      yhk2 = yhk2 + q;
      yhk2 = yhk2*4;
  }
}