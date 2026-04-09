int main1(){
  int kj, xs, bfe, qa79;
  kj=76;
  xs=0;
  bfe=-5;
  qa79=xs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= xs);
  loop invariant (xs <= kj);
  loop invariant bfe <= -5;
  loop invariant qa79 <= 0;
  loop invariant (bfe % 5) == 0;
  loop invariant (qa79 % 5) == 0;
  loop assigns xs, bfe, qa79;
*/
while (1) {
      if (!(xs < kj)) {
          break;
      }
      xs++;
      bfe += qa79;
      qa79 = qa79 + bfe;
  }
}