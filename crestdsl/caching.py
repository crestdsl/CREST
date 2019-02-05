import crestdsl.model as model
import functools

class Cache(object):
    """
    Create a cache for certain model API functions, so that we can work a bit faster.
    Remember to activate/deactivate.
    """

    def __init__(self):
        # save originals
        self.orig_get_entities = model.get_entities
        self.orig_get_all_entities = model.get_all_entities
        self.orig_get_all_ports = model.get_all_ports
        self.orig_get_by_klass = model.entity.get_by_klass

        self._created = False

    def __enter__(self):
        self._cache = Cache()
        self._cache.activate()
        return self._cache

    def __exit__(self, type, value, traceback):
        self._cache.deactivate()

    def create_cached(self):
        def create_cached_function(func):
            @functools.lru_cache(maxsize=1024)
            def new_func(entity, func=func):
                # print("cache miss", func, entity)
                return func(entity)
            return new_func

        def create_cached_get_by_klass(func):
            @functools.lru_cache(maxsize=1024)
            def new_func(class_or_entity, klass, as_dict=False, func=func):
                # print("cache miss", func, class_or_entity, klass, as_dict)
                return func(class_or_entity, klass, as_dict)
            return new_func

        self.cached_get_entities = create_cached_function(model.get_entities)
        self.cached_get_all_entities = create_cached_function(model.get_all_entities)
        self.cached_get_all_ports = create_cached_function(model.get_all_ports)
        self.cached_entity_get_by_klass = create_cached_get_by_klass(model.entity.get_by_klass)

        self._created = True

    def activate(self):
        if not self._created:
            self.create_cached()

        # replace originals
        model.get_entities = self.cached_get_entities
        model.get_all_entities = self.cached_get_all_entities
        model.get_all_ports = self.cached_get_all_ports
        model.entity.get_by_klass = self.cached_entity_get_by_klass

    def deactivate(self):
        # reset to orginals
        model.get_entities = self.orig_get_entities
        model.get_all_entities = self.orig_get_all_entities
        model.get_all_ports = self.orig_get_all_ports
        model.entity.get_by_klass = self.orig_get_by_klass
