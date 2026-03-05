int main1(int n){
  int w, o, nob;

  w=13;
  o=0;
  nob=4;

  while (o<w) {
      nob = o%5;
      if (o>=nob) {
          nob = (o-nob)%5;
          nob = nob+nob-nob;
      }
      else {
          nob = nob + nob;
      }
      o = o + 1;
      n = n + o;
  }

}
