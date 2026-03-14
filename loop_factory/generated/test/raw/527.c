int main1(int r,int j){
  int fi, r0, s2j, jq2;

  fi=j;
  r0=0;
  s2j=0;
  jq2=j;

  while (1) {
      if (!(r0<=fi-1)) {
          break;
      }
      r += r0;
      s2j++;
      jq2 += 1;
      r = r + 3;
      j += r;
      r0 = fi;
  }

}
