int main1(int t,int k){
  int oh, ek, f0l;

  oh=t;
  ek=0;
  f0l=2;

  while (ek<oh) {
      if (f0l==1) {
          f0l = 2;
      }
      else {
          if (f0l==2) {
              f0l = 1;
          }
      }
      k += f0l;
      t += 1;
  }

}
