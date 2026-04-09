int main1(){
  int t7, ktt, v6, a, c;
  t7=1;
  ktt=0;
  v6=t7;
  a=0;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ktt;
  loop invariant ktt <= t7;
  loop invariant v6 == (ktt + 1) * t7 - (ktt * (ktt + 1)) / 2;
  loop invariant a >= 0;
  loop invariant c >= 0;
  loop invariant a == ktt*v6 - ktt*ktt*t7 
                           + (ktt*ktt*(ktt+1))/2 
                           + t7*ktt*(ktt-1)/2 
                           - (ktt*(ktt-1)*(ktt+1))/6;
  loop assigns a, ktt, c, v6;
*/
while (1) {
      if (!(ktt < t7)) {
          break;
      }
      a += v6;
      ktt = ktt + 1;
      c = c + a;
      v6 = v6+t7-ktt;
  }
}