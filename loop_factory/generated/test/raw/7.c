int main1(int m){
  int ue, u, dv;

  ue=51;
  u=0;
  dv=2;

  while (1) {
      if (!(u<ue)) {
          break;
      }
      dv += 2;
      u = u + 1;
      m = m + u;
  }

}
