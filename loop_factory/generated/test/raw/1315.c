int main1(){
  int o, iyrc, k, fy;

  o=0;
  iyrc=(1%28)+10;
  k=-3;
  fy=5;

  while (iyrc>o) {
      iyrc = iyrc - o;
      o = o + 1;
      fy = ((o%3))+(fy);
      k = k*3+5;
  }

}
