int main1(int s){
  int q1, r1, xcyp;

  q1=80;
  r1=0;
  xcyp=0;

  while (1) {
      if (!(xcyp<q1)) {
          break;
      }
      r1 = (r1+1)%5;
      xcyp += 1;
      s = (s+xcyp)%4;
  }

}
