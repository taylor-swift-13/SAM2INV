int main1(){
  int vm, nk, to, y8t, c8l;
  vm=1*2;
  nk=0;
  to=0;
  y8t=0;
  c8l=vm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant to == nk;
  loop invariant c8l == vm + nk*(nk+1)*(nk+2)/6;
  loop invariant nk <= vm;
  loop invariant to <= vm;
  loop invariant y8t == nk*(nk+1)/2;
  loop invariant c8l == 2 + nk*(nk+1)*(nk+2)/6;
  loop invariant c8l == vm + to*(to+1)*(to+2)/6;
  loop invariant nk >= 0;
  loop assigns to, y8t, c8l, nk;
*/
while (1) {
      to += 1;
      y8t = y8t + to;
      c8l = c8l + y8t;
      nk++;
      if (nk>=vm) {
          break;
      }
  }
}