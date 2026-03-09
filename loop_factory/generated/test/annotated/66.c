int main1(){
  int l, m684, gjwe;
  l=(1%29)+6;
  m684=0;
  gjwe=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m684 >= 0;
  loop invariant m684 + gjwe == l;
  loop invariant m684 <= l + 1;
  loop invariant (m684 % 2) == 0;
  loop assigns m684, gjwe;
*/
while (m684<l&&gjwe>0) {
      m684++;
      gjwe--;
      gjwe--;
      m684++;
  }
}