int main1(){
  int wv, u3n;
  wv=1;
  u3n=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wv == 1;
  loop invariant u3n >= 1;
  loop invariant u3n % 2 == 1;
  loop invariant u3n <= 3;
  loop assigns u3n;
*/
while (u3n<=wv) {
      u3n += u3n;
      u3n += 1;
  }
}