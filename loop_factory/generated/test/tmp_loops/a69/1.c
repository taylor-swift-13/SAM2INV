int main1(){
  int s9, i, o4, v0m, oj, kj, lmps, tu, ht;

  s9=1+7;
  i=0;
  o4=41;
  v0m=0;
  oj=1;
  kj=0;
  lmps=i;
  tu=i;
  ht=i;

  while (1) {
      if (!(o4>0&&i<s9)) {
          break;
      }
      if (o4<oj) {
          kj = o4;
      }
      else {
          kj = oj;
      }
      o4 = o4 - kj;
      v0m = v0m + kj;
      if (i%2==0) {
          oj += 2;
      }
      else {
          oj++;
      }
      i = i + 1;
      lmps = lmps + v0m;
      tu = tu*tu;
      lmps = lmps + i;
      ht = ht+lmps*tu;
  }

}
