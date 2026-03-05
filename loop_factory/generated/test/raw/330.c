int main1(int s){
  int r, k, eam;

  r=(s%27)+5;
  k=r;
  eam=s;

  while (k>=1) {
      if (k<r/2) {
          eam = eam + eam;
      }
      else {
          eam++;
      }
      s += r;
  }

}
