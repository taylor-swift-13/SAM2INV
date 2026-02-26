int main1(int a,int k){
  int b, x, c;

  b=70;
  x=2;
  c=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 2;
  loop invariant x <= b;
  loop invariant b == 70;
  loop invariant c == 2 || c == k+2;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 2 <= x;
  loop invariant (2 <= x && x <= b && a == \at(a, Pre) && b == 70);
  loop invariant (k == \at(k, Pre) && (c == 2 || c == k+2));
  loop invariant 2 <= x <= b;
  loop assigns x, c;
*/
while (x<=b-1) {
      if (a<b+1) {
          c = k+2;
      }
      x = x+1;
  }

}
