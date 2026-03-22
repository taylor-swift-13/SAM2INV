int main1(){
  int rg, fi, gski, lzn;

  rg=23;
  fi=rg;
  gski=(1%20)+10;
  lzn=(1%15)+8;

  while (1) {
      if (!(gski>0&&lzn>0)) {
          break;
      }
      if (fi%2==0) {
          gski -= 1;
      }
      else {
          lzn -= 1;
      }
      fi = fi + 1;
  }

}
