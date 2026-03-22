int main1(){
  int we, im, ik, h, efa, dp, jl, k;
  we=74;
  im=-1;
  ik=13;
  h=10;
  efa=0;
  dp=we;
  jl=3;
  k=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == im;
  loop invariant ik + h == 23;
  loop invariant jl == 3 + we * (im + 1);
  loop invariant (im >= -1);
  loop invariant (im <= we);
  loop invariant dp >= 74;
  loop invariant efa == ((im + 1) % 2);
  loop invariant jl == 3 + we * (k + 1);
  loop invariant dp == we + (im + 1) + (im + 6) / 6;
  loop assigns ik, h, efa, im, dp, k, jl;
*/
while (im<we) {
      if (efa==0) {
          ik += 1;
          h = h - 1;
          efa = 1;
      }
      else {
          ik = ik - 1;
          h += 1;
          efa = 0;
      }
      im++;
      if ((im%6)==0) {
          dp += 1;
      }
      dp += 1;
      k += 1;
      jl += we;
  }
}