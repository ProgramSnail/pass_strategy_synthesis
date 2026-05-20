### C++ pseudocode
```cpp
// external

struct Data { /*...*/ };
struct DateTime { /*...*/ };

Request init() { /*...*/ }
Version old_version_placeholder() { /*...*/ }
bool new_api_activated() { /*...*/ }
void do_request(const Remote& remote, const Request& r) { /*...*/ }
Data convert_to_new_data(const Data& data) { /*...*/ }
string name_to_new_format(const string& name) { /*...*/ }
DateTime current_time() { /*...*/ }
bool no_errors() { /*...*/ }
void log_write(int x) { /*...*/ }

// structures

struct UserUtils {
  int id;
  vector<int> connected_users;
};

struct UserInfo {
  string name;
  string surname;
  int age;
};

struct User {
  UserUtils* utils;
  PersonalInfo* info;
};

struct Version {
  int id;
  DateTime release_date;
  vector<int> supported_stds;
};

struct Utils {
  bool has_version;
  int id;
};

struct Request {
  User* user;
  Version* version;
  Utils* utils;
  Data* data;
  DateTime time;
};

// example itself

int get_version_id(Request /*[?]*/ r) {
  if (r.utils.has_version) {
    return r.version.id;
  }
  return old_version_placeholder().id;
}

Version updated_version(Request /*[?]*/ r) {
  if (not r.utils.has_version) {
    return old_version_placeholder();
  }
  return r.vestion;
}

void send(const Remote& remote, Request /*[?]*/ r) {
  if (new_api_activated()) {
    r.utils.has_version = true;
    r.data = convert_to_new_data(r.data);
    r.user.info.name =
      name_to_new_format(r.user.info.name);
  }
  r.time = current_time();
  do_request(remote, r);
}

void send_all(const vector<Remote>& remotes) {
  Request r = init();
  for(const auto& remote : remotes) {
    send(remote, r);
    log_write(get_version_id(r));
  }
  r.version = updated_version(r);
  if (no_errors()) {
    print("Done requests for user {}", r.user.utils.id);
  } else {
    print("Error during send of {}", r.utils.id);
  }
}
```

### DSL pseudocode
```python

# structures

UserUtils := [(); ()] # id, connected_users

UserInfo := [(); (); ()] # name, surname, age

User := [& UserUtils; & UserInfo] # utils, info
# or User := [& [(); ()]; & [(); (); ()]] # utils, info

Version := [(); (); ()] # id, release_date, supported_stds

Utils := [(); ()] # has_version, id

Request := [& User; # user
            & Version; # version
            & Utils; # utils
            & (); # data
            ()] # time
# or Request := [& [& [(); ()], & [(); (); ()]]; # user
#                & [(); (); ()]; # version
#                & [(); ()]; # utils
#                & (); # data
#                ()] # time

# example itself

get_version_id(r : Request) {
  read(r.version.id) | skip
}

updated_version(r : Request) {
  read(r.utils.has_version);
  read(r.version)
}

send(r : Request) {
  ((write(r.utils.has_version);
    convert_to_new_data(r.data); # -> read(r.data)
    write(r.data);
    name_to_new_format(r.user.info.name); # -> read(r.user.info.name)
    write(r.user.info.name))
   | skip);
  write(r.time);
  do_request(r) # -> read(r)
}

send_all(r : Request) { # NOTE: add argument to not place body on top level
  write(r);
  send(r);
  get_version_id(r);

  updated_version(r);
  write(r.version);

  (read(r.user.utils.id) | read(r.utils.id))
}

send_all(r)
```
`

### Actual representation
In `analyzer.ml` & `synthesizer.ml`

### DSL result
```
TODO
```

### C++ result
```
TODO
```
