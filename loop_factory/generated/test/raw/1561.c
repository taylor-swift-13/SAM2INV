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
