int main1(int t,int j){
  int kp, crj, w, fb;

  kp=185;
  crj=1;
  w=1;
  fb=j;

  while (1) {
      if (!(crj<=kp/2)) {
          break;
      }
      fb = fb*fb+w;
      crj = crj*2;
  }

}
