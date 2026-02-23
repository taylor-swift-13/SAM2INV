int main1(int a,int k){
  int b, x, c;

  b=70;
  x=b+3;
  c=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 70;
  loop invariant x <= b + 3;
  loop invariant x >= b;
  loop invariant c >= -3;
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant x <= 73;
  loop invariant c == -3;

  loop assigns x, c;
*/
while (x>=b+1) {
      if (x+7<=c+b) {
          c = c*c+c;
      }
      x = x-1;
  }

}
